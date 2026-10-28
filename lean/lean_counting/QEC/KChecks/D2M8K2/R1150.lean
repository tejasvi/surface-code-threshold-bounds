import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4600 = true := by
  decide +kernel

theorem tot4600 : totK PD2M8K2 D2M8K2.t4600 = [0, 0, 0, 153465825276, 471732291815, 224632555644, 13583963893, 0] := by
  decide +kernel

theorem rows4601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4601 = true := by
  decide +kernel

theorem tot4601 : totK PD2M8K2 D2M8K2.t4601 = [0, 0, 0, 0, 364136333630, 431993085863, 49497358005, 0] := by
  decide +kernel

theorem rows4602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4602 = true := by
  decide +kernel

theorem tot4602 : totK PD2M8K2 D2M8K2.t4602 = [0, 0, 0, 167363779947, 414356658873, 234249888067, 50780121326, 1330264907] := by
  decide +kernel

theorem rows4603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4603 = true := by
  decide +kernel

theorem tot4603 : totK PD2M8K2 D2M8K2.t4603 = [0, 0, 0, 244817347103, 467765168455, 178188149361, 8625549670, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
