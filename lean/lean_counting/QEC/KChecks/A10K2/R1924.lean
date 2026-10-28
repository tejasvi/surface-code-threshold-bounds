import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7696 = true := by
  decide +kernel

theorem tot7696 : totK PA10K2 A10K2.t7696 = [0, 0, 0, 300091966344, 1413226022204, 2148019523673, 1007875933356, 81012775032, 0, 0] := by
  decide +kernel

theorem rows7697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7697 = true := by
  decide +kernel

theorem tot7697 : totK PA10K2 A10K2.t7697 = [0, 0, 0, 232863291506, 1019977352675, 1871212412587, 1490966390520, 350509730235, 13572172291, 0] := by
  decide +kernel

theorem rows7698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7698 = true := by
  decide +kernel

theorem tot7698 : totK PA10K2 A10K2.t7698 = [0, 0, 0, 509705371753, 1906459597312, 2034971763676, 543320777558, 25519223071, 0, 0] := by
  decide +kernel

theorem rows7699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7699 = true := by
  decide +kernel

theorem tot7699 : totK PA10K2 A10K2.t7699 = [0, 0, 0, 100738380669, 1153279060121, 2371628472429, 1341960110835, 159873350637, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
