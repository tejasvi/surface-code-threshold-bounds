import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12892 = true := by
  decide +kernel

theorem tot12892 : totK PD2M8K2 D2M8K2.t12892 = [0, 47142334795, 322090144767, 436587187196, 89807414597, 1164319620, 0, 0] := by
  decide +kernel

theorem rows12893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12893 = true := by
  decide +kernel

theorem tot12893 : totK PD2M8K2 D2M8K2.t12893 = [0, 0, 197337040102, 472467439098, 188757328665, 11885407614, 0, 0] := by
  decide +kernel

theorem rows12894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12894 = true := by
  decide +kernel

theorem tot12894 : totK PD2M8K2 D2M8K2.t12894 = [0, 173598046017, 461405845749, 242831817808, 23012816066, 0, 0, 0] := by
  decide +kernel

theorem rows12895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12895 = true := by
  decide +kernel

theorem tot12895 : totK PD2M8K2 D2M8K2.t12895 = [0, 151301247379, 463637135174, 260152871262, 15153993480, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
