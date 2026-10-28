import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15484 = true := by
  decide +kernel

theorem tot15484 : totK PD2M8K2 D2M8K2.t15484 = [0, 0, 241760174825, 503975255477, 150008077012, 2304167554, 0, 0] := by
  decide +kernel

theorem rows15485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15485 = true := by
  decide +kernel

theorem tot15485 : totK PD2M8K2 D2M8K2.t15485 = [0, 0, 180542328616, 466005709276, 220584806970, 12667552787, 0, 0] := by
  decide +kernel

theorem rows15486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15486 = true := by
  decide +kernel

theorem tot15486 : totK PD2M8K2 D2M8K2.t15486 = [0, 0, 197776330310, 483746754243, 204024395052, 12413128817, 0, 0] := by
  decide +kernel

theorem rows15487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15487 = true := by
  decide +kernel

theorem tot15487 : totK PD2M8K2 D2M8K2.t15487 = [0, 0, 139580306287, 453172292738, 291791388219, 21709594046, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
