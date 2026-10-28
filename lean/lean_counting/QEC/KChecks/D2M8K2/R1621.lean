import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6484 = true := by
  decide +kernel

theorem tot6484 : totK PD2M8K2 D2M8K2.t6484 = [187096952973, 454428471785, 236826677609, 17062814301, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6485 = true := by
  decide +kernel

theorem tot6485 : totK PD2M8K2 D2M8K2.t6485 = [40569491811, 341542352708, 426951585374, 82286083284, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows6486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6486 = true := by
  decide +kernel

theorem tot6486 : totK PD2M8K2 D2M8K2.t6486 = [26607506368, 274022727661, 477859439673, 122925662866, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows6487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6487 = true := by
  decide +kernel

theorem tot6487 : totK PD2M8K2 D2M8K2.t6487 = [170120188027, 446643752838, 279553408698, 30281783105, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
