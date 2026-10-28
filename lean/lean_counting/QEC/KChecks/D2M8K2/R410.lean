import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1640 = true := by
  decide +kernel

theorem tot1640 : totK PD2M8K2 D2M8K2.t1640 = [0, 156460576773, 450927431510, 257373426743, 18182990193, 0, 0, 0] := by
  decide +kernel

theorem rows1641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1641 = true := by
  decide +kernel

theorem tot1641 : totK PD2M8K2 D2M8K2.t1641 = [0, 89411507079, 344549840212, 383329189439, 85334847331, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1642 = true := by
  decide +kernel

theorem tot1642 : totK PD2M8K2 D2M8K2.t1642 = [0, 0, 328851765328, 516470666853, 66454366038, 0, 0, 0] := by
  decide +kernel

theorem rows1643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1643 = true := by
  decide +kernel

theorem tot1643 : totK PD2M8K2 D2M8K2.t1643 = [0, 203739346664, 463641691591, 232199127230, 14460355466, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
