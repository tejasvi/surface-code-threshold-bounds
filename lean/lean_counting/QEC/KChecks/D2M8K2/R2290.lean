import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9160 = true := by
  decide +kernel

theorem tot9160 : totK PD2M8K2 D2M8K2.t9160 = [160421186954, 443928520369, 282997203272, 32535664943, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9161 = true := by
  decide +kernel

theorem tot9161 : totK PD2M8K2 D2M8K2.t9161 = [188547599962, 474144505614, 222674495059, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9162 = true := by
  decide +kernel

theorem tot9162 : totK PD2M8K2 D2M8K2.t9162 = [61933783068, 318835554971, 422708537825, 91970816601, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows9163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9163 = true := by
  decide +kernel

theorem tot9163 : totK PD2M8K2 D2M8K2.t9163 = [0, 197298387037, 465744506080, 196480636061, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
