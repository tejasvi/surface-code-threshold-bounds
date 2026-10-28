import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4680 = true := by
  decide +kernel

theorem tot4680 : totK PA10K2 A10K2.t4680 = [0, 0, 574736170080, 1841414585313, 1800630093229, 453629601242, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows4681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4681 = true := by
  decide +kernel

theorem tot4681 : totK PA10K2 A10K2.t4681 = [0, 0, 0, 1135963815087, 2394393566959, 941528435356, 70010502433, 0, 0, 0] := by
  decide +kernel

theorem rows4682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4682 = true := by
  decide +kernel

theorem tot4682 : totK PA10K2 A10K2.t4682 = [0, 280546762594, 1157072088751, 1574188999089, 1137790743206, 639758005216, 144586921448, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4683 = true := by
  decide +kernel

theorem tot4683 : totK PA10K2 A10K2.t4683 = [0, 514125768247, 1753037611926, 1932967369860, 760510971556, 72263901834, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
