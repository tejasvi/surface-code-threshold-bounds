import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7036 = true := by
  decide +kernel

theorem tot7036 : totK PA10K2 A10K2.t7036 = [0, 479892249523, 1701657062178, 1902338426147, 757130127064, 80016036000, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7037 = true := by
  decide +kernel

theorem tot7037 : totK PA10K2 A10K2.t7037 = [0, 416542488315, 1776545966204, 2157955945136, 699608434342, 35547674163, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7038 = true := by
  decide +kernel

theorem tot7038 : totK PA10K2 A10K2.t7038 = [0, 0, 562356278322, 2047379954852, 1960118203202, 391577490159, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows7039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7039 = true := by
  decide +kernel

theorem tot7039 : totK PA10K2 A10K2.t7039 = [0, 0, 517313452539, 1810183776990, 1942824065669, 662732445287, 56143165367, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
