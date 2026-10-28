import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11364 = true := by
  decide +kernel

theorem tot11364 : totK PD2M8K2 D2M8K2.t11364 = [192172715236, 478550349733, 218965969170, 12313900984, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11365 = true := by
  decide +kernel

theorem tot11365 : totK PD2M8K2 D2M8K2.t11365 = [0, 289400155013, 503362637914, 108459147594, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows11366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11366 = true := by
  decide +kernel

theorem tot11366 : totK PD2M8K2 D2M8K2.t11366 = [21207688736, 214203850134, 449687139822, 183024418617, 11846586184, 0, 0, 0] := by
  decide +kernel

theorem rows11367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11367 = true := by
  decide +kernel

theorem tot11367 : totK PD2M8K2 D2M8K2.t11367 = [190221868386, 461072906318, 247312510927, 23208008898, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
