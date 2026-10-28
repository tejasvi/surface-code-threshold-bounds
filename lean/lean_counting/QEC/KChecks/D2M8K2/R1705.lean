import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6820 = true := by
  decide +kernel

theorem tot6820 : totK PD2M8K2 D2M8K2.t6820 = [0, 40721127434, 370683144498, 429415448928, 44746449299, 0, 0, 0] := by
  decide +kernel

theorem rows6821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6821 = true := by
  decide +kernel

theorem tot6821 : totK PD2M8K2 D2M8K2.t6821 = [0, 173551729103, 448768584821, 268847331519, 29170957262, 0, 0, 0] := by
  decide +kernel

theorem rows6822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6822 = true := by
  decide +kernel

theorem tot6822 : totK PD2M8K2 D2M8K2.t6822 = [0, 200314567924, 495884356221, 205527966102, 7887122479, 0, 0, 0] := by
  decide +kernel

theorem rows6823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6823 = true := by
  decide +kernel

theorem tot6823 : totK PD2M8K2 D2M8K2.t6823 = [0, 174665947218, 464035740266, 242735515457, 21095398144, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
