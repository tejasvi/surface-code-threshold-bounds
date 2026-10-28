import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9820 = true := by
  decide +kernel

theorem tot9820 : totK PD2M8K2 D2M8K2.t9820 = [0, 0, 177373872714, 456368104265, 252045024232, 15299512318, 0, 0] := by
  decide +kernel

theorem rows9821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9821 = true := by
  decide +kernel

theorem tot9821 : totK PD2M8K2 D2M8K2.t9821 = [0, 122380221654, 334743506292, 290545238956, 140584437932, 13566920432, 0, 0] := by
  decide +kernel

theorem rows9822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9822 = true := by
  decide +kernel

theorem tot9822 : totK PD2M8K2 D2M8K2.t9822 = [0, 189812271089, 454411369746, 229997313130, 17111997474, 0, 0, 0] := by
  decide +kernel

theorem rows9823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9823 = true := by
  decide +kernel

theorem tot9823 : totK PD2M8K2 D2M8K2.t9823 = [0, 105439490428, 428191307740, 328809680482, 31250517957, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
