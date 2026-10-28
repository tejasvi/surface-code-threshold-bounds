import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7192 = true := by
  decide +kernel

theorem tot7192 : totK PA10K2 A10K2.t7192 = [0, 0, 131301146874, 1361777218011, 2284835350209, 826593296341, 58503570348, 0, 0, 0] := by
  decide +kernel

theorem rows7193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7193 = true := by
  decide +kernel

theorem tot7193 : totK PA10K2 A10K2.t7193 = [0, 0, 315590801309, 1250234316094, 1817117899535, 1073327414950, 227545341017, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7194 = true := by
  decide +kernel

theorem tot7194 : totK PA10K2 A10K2.t7194 = [0, 0, 523813060156, 1864492963318, 1933063125361, 496632161002, 18560348465, 0, 0, 0] := by
  decide +kernel

theorem rows7195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7195 = true := by
  decide +kernel

theorem tot7195 : totK PA10K2 A10K2.t7195 = [0, 0, 0, 670725266455, 2017696409525, 1633268858874, 387345159397, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
