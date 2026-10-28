import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5936 = true := by
  decide +kernel

theorem tot5936 : totK PA10K2 A10K2.t5936 = [0, 499628035384, 1856130040287, 1967675104175, 569341579651, 23595873998, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5937 = true := by
  decide +kernel

theorem tot5937 : totK PA10K2 A10K2.t5937 = [0, 0, 723701368077, 2207523265912, 1614926221933, 278698149716, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows5938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5938 = true := by
  decide +kernel

theorem tot5938 : totK PA10K2 A10K2.t5938 = [0, 511318055732, 1833490158290, 2028709444899, 743571505765, 70302048286, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5939 = true := by
  decide +kernel

theorem tot5939 : totK PA10K2 A10K2.t5939 = [0, 83903912032, 844929314484, 2194275391531, 1708747081407, 302998734044, 7047025452, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
