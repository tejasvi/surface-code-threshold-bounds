import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t916 = true := by
  decide +kernel

theorem tot916 : totK PA10K2 A10K2.t916 = [0, 0, 482322158909, 1653277700024, 1924277069429, 736332945163, 69333217803, 0, 0, 0] := by
  decide +kernel

theorem rows917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t917 = true := by
  decide +kernel

theorem tot917 : totK PA10K2 A10K2.t917 = [0, 0, 295824282370, 1562559933592, 2203340867153, 837098217256, 61154536716, 0, 0, 0] := by
  decide +kernel

theorem rows918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t918 = true := by
  decide +kernel

theorem tot918 : totK PA10K2 A10K2.t918 = [0, 0, 209823806281, 1069988794858, 1992636382604, 1335699563594, 248458654947, 7151180950, 0, 0] := by
  decide +kernel

theorem rows919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t919 = true := by
  decide +kernel

theorem tot919 : totK PA10K2 A10K2.t919 = [0, 0, 560515466438, 1983811779986, 1986300195370, 497075614114, 18515547658, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
