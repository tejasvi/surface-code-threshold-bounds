import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14604 = true := by
  decide +kernel

theorem tot14604 : totK PD2M8K2 D2M8K2.t14604 = [0, 18617230336, 281940894211, 490063685893, 97320881244, 1164319620, 0, 0] := by
  decide +kernel

theorem rows14605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14605 = true := by
  decide +kernel

theorem tot14605 : totK PD2M8K2 D2M8K2.t14605 = [0, 196963699570, 468254343904, 228151819187, 19333710703, 0, 0, 0] := by
  decide +kernel

theorem rows14606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14606 = true := by
  decide +kernel

theorem tot14606 : totK PD2M8K2 D2M8K2.t14606 = [0, 187951572174, 464316679386, 219626269926, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows14607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14607 = true := by
  decide +kernel

theorem tot14607 : totK PD2M8K2 D2M8K2.t14607 = [0, 19358310964, 300034436340, 473292152616, 98348272840, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
