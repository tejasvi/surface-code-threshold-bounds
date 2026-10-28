import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2736 = true := by
  decide +kernel

theorem tot2736 : totK PA10K2 A10K2.t2736 = [0, 0, 278580461261, 1239053420590, 1895563781073, 1074995381526, 169107924958, 5447185874, 0, 0] := by
  decide +kernel

theorem rows2737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2737 = true := by
  decide +kernel

theorem tot2737 : totK PA10K2 A10K2.t2737 = [0, 0, 495069661058, 1747405476495, 1826535480557, 598359321109, 51464731716, 0, 0, 0] := by
  decide +kernel

theorem rows2738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2738 = true := by
  decide +kernel

theorem tot2738 : totK PA10K2 A10K2.t2738 = [0, 0, 0, 972988700317, 2421523217650, 1166578208008, 105828952891, 0, 0, 0] := by
  decide +kernel

theorem rows2739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2739 = true := by
  decide +kernel

theorem tot2739 : totK PA10K2 A10K2.t2739 = [0, 0, 480593849206, 1538118764950, 1661795015000, 913207264816, 193814237053, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
