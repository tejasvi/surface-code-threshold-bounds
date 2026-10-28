import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6608 = true := by
  decide +kernel

theorem tot6608 : totK PA10K2 A10K2.t6608 = [0, 0, 0, 778369214068, 2248642743325, 1521892777658, 259690869459, 7237400819, 0, 0] := by
  decide +kernel

theorem rows6609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6609 = true := by
  decide +kernel

theorem tot6609 : totK PA10K2 A10K2.t6609 = [0, 0, 503849805566, 1872939550059, 2048552334382, 662081892332, 44255908442, 0, 0, 0] := by
  decide +kernel

theorem rows6610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6610 = true := by
  decide +kernel

theorem tot6610 : totK PA10K2 A10K2.t6610 = [0, 194473833962, 730812099200, 1571453352315, 1831925557159, 708277222871, 57551169768, 0, 0, 0] := by
  decide +kernel

theorem rows6611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6611 = true := by
  decide +kernel

theorem tot6611 : totK PA10K2 A10K2.t6611 = [0, 433653765824, 1750710665292, 1946838269319, 557050005168, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
