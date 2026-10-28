import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15688 = true := by
  decide +kernel

theorem tot15688 : totK PD2M8K2 D2M8K2.t15688 = [0, 0, 191764872485, 467346178050, 249662987304, 17941154095, 0, 0] := by
  decide +kernel

theorem rows15689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15689 = true := by
  decide +kernel

theorem tot15689 : totK PD2M8K2 D2M8K2.t15689 = [0, 0, 199550654527, 471786320625, 218935658326, 10771691989, 0, 0] := by
  decide +kernel

theorem rows15690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15690 = true := by
  decide +kernel

theorem tot15690 : totK PD2M8K2 D2M8K2.t15690 = [0, 0, 23716108948, 314892982089, 462492093105, 98756643189, 1268739303, 0] := by
  decide +kernel

theorem rows15691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15691 = true := by
  decide +kernel

theorem tot15691 : totK PD2M8K2 D2M8K2.t15691 = [0, 0, 0, 238348965638, 495851941228, 148314172136, 4892834540, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
