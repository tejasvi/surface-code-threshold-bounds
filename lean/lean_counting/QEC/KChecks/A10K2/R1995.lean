import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7980 = true := by
  decide +kernel

theorem tot7980 : totK PA10K2 A10K2.t7980 = [0, 0, 0, 118860215929, 1013272159330, 2197194128597, 1377761055811, 200461704806, 6318667960, 0] := by
  decide +kernel

theorem rows7981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7981 = true := by
  decide +kernel

theorem tot7981 : totK PA10K2 A10K2.t7981 = [0, 0, 0, 297798990022, 1454068001239, 2113398764948, 890948384769, 84409757097, 0, 0] := by
  decide +kernel

theorem rows7982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7982 = true := by
  decide +kernel

theorem tot7982 : totK PA10K2 A10K2.t7982 = [0, 0, 0, 464269883445, 1819546536079, 2037825882772, 661282956019, 50414133861, 0, 0] := by
  decide +kernel

theorem rows7983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7983 = true := by
  decide +kernel

theorem tot7983 : totK PA10K2 A10K2.t7983 = [0, 0, 0, 122576024678, 950828477143, 2092623662153, 1470605843645, 226738269337, 6439430839, 0] := by
  decide +kernel

end QECKChecks.A10K2
