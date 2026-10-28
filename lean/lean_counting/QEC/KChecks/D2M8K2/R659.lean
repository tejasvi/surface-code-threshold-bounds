import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2636 = true := by
  decide +kernel

theorem tot2636 : totK PD2M8K2 D2M8K2.t2636 = [0, 14392747747, 272317990654, 488085130746, 122725412029, 2498823382, 0, 0] := by
  decide +kernel

theorem rows2637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2637 = true := by
  decide +kernel

theorem tot2637 : totK PD2M8K2 D2M8K2.t2637 = [0, 198129061797, 472575184121, 236230241561, 22016217787, 0, 0, 0] := by
  decide +kernel

theorem rows2638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2638 = true := by
  decide +kernel

theorem tot2638 : totK PD2M8K2 D2M8K2.t2638 = [0, 190511521891, 462138118093, 231135448880, 15909660794, 0, 0, 0] := by
  decide +kernel

theorem rows2639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2639 = true := by
  decide +kernel

theorem tot2639 : totK PD2M8K2 D2M8K2.t2639 = [0, 19691318959, 325696421584, 472965435986, 87249594838, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
