import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5012 = true := by
  decide +kernel

theorem tot5012 : totK PD2M8K2 D2M8K2.t5012 = [0, 0, 229058055577, 495501704824, 163045624214, 9404247146, 0, 0] := by
  decide +kernel

theorem rows5013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5013 = true := by
  decide +kernel

theorem tot5013 : totK PD2M8K2 D2M8K2.t5013 = [0, 155406381531, 393521469318, 275219437984, 56531179169, 2481160468, 0, 0] := by
  decide +kernel

theorem rows5014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5014 = true := by
  decide +kernel

theorem tot5014 : totK PD2M8K2 D2M8K2.t5014 = [0, 170824264471, 439568360304, 278511313479, 30251837770, 0, 0, 0] := by
  decide +kernel

theorem rows5015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5015 = true := by
  decide +kernel

theorem tot5015 : totK PD2M8K2 D2M8K2.t5015 = [0, 95626219555, 402138689429, 325999466070, 47676473183, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
