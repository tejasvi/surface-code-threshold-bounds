import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7044 = true := by
  decide +kernel

theorem tot7044 : totK PA10K2 A10K2.t7044 = [0, 0, 67599317612, 799715477455, 2120902742593, 1606793163864, 254738565290, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7045 = true := by
  decide +kernel

theorem tot7045 : totK PA10K2 A10K2.t7045 = [0, 0, 496181907367, 1841617555659, 1970677508255, 560031205308, 23620721234, 0, 0, 0] := by
  decide +kernel

theorem rows7046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7046 = true := by
  decide +kernel

theorem tot7046 : totK PA10K2 A10K2.t7046 = [0, 0, 331364255318, 1576184560559, 2180576216749, 856097507705, 62762815243, 0, 0, 0] := by
  decide +kernel

theorem rows7047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7047 = true := by
  decide +kernel

theorem tot7047 : totK PA10K2 A10K2.t7047 = [0, 0, 0, 537656521485, 2011061672742, 1977755979523, 404848713711, 12224107035, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
