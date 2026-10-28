import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2852 = true := by
  decide +kernel

theorem tot2852 : totK PA10K2 A10K2.t2852 = [0, 327291078893, 1491168709988, 2133743239167, 898914480202, 62723358326, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2853 = true := by
  decide +kernel

theorem tot2853 : totK PA10K2 A10K2.t2853 = [0, 0, 611209916509, 2047061533139, 1887740732384, 394073363601, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows2854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2854 = true := by
  decide +kernel

theorem tot2854 : totK PA10K2 A10K2.t2854 = [0, 320479959089, 1093146103422, 1566405183084, 1400263461192, 532446636494, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows2855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2855 = true := by
  decide +kernel

theorem tot2855 : totK PA10K2 A10K2.t2855 = [0, 540929702963, 1957780899705, 1904197367121, 415551326579, 12129354050, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
