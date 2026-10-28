import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7112 = true := by
  decide +kernel

theorem tot7112 : totK PA10K2 A10K2.t7112 = [0, 0, 469041720940, 1780284688361, 1958867886954, 523660907485, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows7113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7113 = true := by
  decide +kernel

theorem tot7113 : totK PA10K2 A10K2.t7113 = [0, 0, 545863650564, 1925854837649, 1916758554463, 456655148922, 13149917422, 0, 0, 0] := by
  decide +kernel

theorem rows7114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7114 = true := by
  decide +kernel

theorem tot7114 : totK PA10K2 A10K2.t7114 = [0, 0, 516559263158, 1818855775697, 1835505099469, 467244080779, 30637645759, 0, 0, 0] := by
  decide +kernel

theorem rows7115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7115 = true := by
  decide +kernel

theorem tot7115 : totK PA10K2 A10K2.t7115 = [0, 0, 75885760832, 1245897314856, 2344551875339, 891823634752, 63910416283, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
