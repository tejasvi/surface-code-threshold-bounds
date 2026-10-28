import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1728 = true := by
  decide +kernel

theorem tot1728 : totK PA10K2 A10K2.t1728 = [0, 0, 0, 633418228287, 2069566505340, 1665075655348, 288626068012, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1729 = true := by
  decide +kernel

theorem tot1729 : totK PA10K2 A10K2.t1729 = [0, 0, 0, 482023766921, 1818648658187, 2004629781992, 528404446765, 31987876949, 0, 0] := by
  decide +kernel

theorem rows1730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1730 = true := by
  decide +kernel

theorem tot1730 : totK PA10K2 A10K2.t1730 = [0, 0, 0, 512553111987, 1956100323056, 1856418844639, 401224028872, 12322100762, 0, 0] := by
  decide +kernel

theorem rows1731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1731 = true := by
  decide +kernel

theorem tot1731 : totK PA10K2 A10K2.t1731 = [0, 0, 0, 497800813112, 1772909869269, 1825351697421, 459416306162, 31088438951, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
