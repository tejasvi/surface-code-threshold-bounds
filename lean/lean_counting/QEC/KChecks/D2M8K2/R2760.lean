import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11040 = true := by
  decide +kernel

theorem tot11040 : totK PD2M8K2 D2M8K2.t11040 = [0, 34152374823, 353281187694, 414785378829, 62342033293, 1053411165, 0, 0] := by
  decide +kernel

theorem rows11041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11041 = true := by
  decide +kernel

theorem tot11041 : totK PD2M8K2 D2M8K2.t11041 = [0, 76167677528, 295405099053, 385416945546, 96365418252, 3667207281, 0, 0] := by
  decide +kernel

theorem rows11042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11042 = true := by
  decide +kernel

theorem tot11042 : totK PD2M8K2 D2M8K2.t11042 = [0, 159127014538, 456652514089, 260052795576, 23328842403, 0, 0, 0] := by
  decide +kernel

theorem rows11043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11043 = true := by
  decide +kernel

theorem tot11043 : totK PD2M8K2 D2M8K2.t11043 = [33270956665, 177388144399, 415582735579, 254139420859, 22092694014, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
