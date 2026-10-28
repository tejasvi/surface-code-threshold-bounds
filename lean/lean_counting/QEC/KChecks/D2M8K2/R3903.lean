import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15612 = true := by
  decide +kernel

theorem tot15612 : totK PD2M8K2 D2M8K2.t15612 = [0, 0, 269342784565, 505392067232, 105060303042, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15613 = true := by
  decide +kernel

theorem tot15613 : totK PD2M8K2 D2M8K2.t15613 = [0, 162872193368, 412459756008, 317992228630, 35614690645, 0, 0, 0] := by
  decide +kernel

theorem rows15614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15614 = true := by
  decide +kernel

theorem tot15614 : totK PD2M8K2 D2M8K2.t15614 = [0, 174012579031, 477382107351, 244480038196, 14697843674, 0, 0, 0] := by
  decide +kernel

theorem rows15615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15615 = true := by
  decide +kernel

theorem tot15615 : totK PD2M8K2 D2M8K2.t15615 = [0, 70151795722, 329068516444, 377245418432, 130029530671, 9935383930, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
