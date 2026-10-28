import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5868 = true := by
  decide +kernel

theorem tot5868 : totK PD2M8K2 D2M8K2.t5868 = [190072402314, 451466083514, 256681361550, 27599236412, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5869 = true := by
  decide +kernel

theorem tot5869 : totK PD2M8K2 D2M8K2.t5869 = [110855835355, 423955007807, 341999493811, 30579053068, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5870 = true := by
  decide +kernel

theorem tot5870 : totK PD2M8K2 D2M8K2.t5870 = [0, 225977307318, 493407694805, 173289989216, 4942026672, 0, 0, 0] := by
  decide +kernel

theorem rows5871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5871 = true := by
  decide +kernel

theorem tot5871 : totK PD2M8K2 D2M8K2.t5871 = [0, 187715793228, 460036890915, 224422896670, 17064697274, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
