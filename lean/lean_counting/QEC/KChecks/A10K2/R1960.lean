import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7840 = true := by
  decide +kernel

theorem tot7840 : totK PA10K2 A10K2.t7840 = [0, 0, 225308319829, 1290310448314, 2187699114481, 1157832511002, 139759311597, 0, 0, 0] := by
  decide +kernel

theorem rows7841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7841 = true := by
  decide +kernel

theorem tot7841 : totK PA10K2 A10K2.t7841 = [0, 0, 61267853542, 696270085677, 1787606400520, 1568967632591, 432109137613, 31082886609, 0, 0] := by
  decide +kernel

theorem rows7842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7842 = true := by
  decide +kernel

theorem tot7842 : totK PA10K2 A10K2.t7842 = [0, 0, 523118927192, 1880230304075, 1863580890048, 456925990040, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows7843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7843 = true := by
  decide +kernel

theorem tot7843 : totK PA10K2 A10K2.t7843 = [0, 0, 99746533768, 883132704292, 2090237247061, 1320222041863, 202134397092, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
