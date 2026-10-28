import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4672 = true := by
  decide +kernel

theorem tot4672 : totK PA10K2 A10K2.t4672 = [0, 489539926130, 1801896430349, 1952905861515, 558698707751, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4673 = true := by
  decide +kernel

theorem tot4673 : totK PA10K2 A10K2.t4673 = [0, 0, 720262889631, 2106325124850, 1683734494840, 394681296643, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4674 = true := by
  decide +kernel

theorem tot4674 : totK PA10K2 A10K2.t4674 = [0, 210879963298, 1017246693929, 1825744982675, 1355909960697, 245039042927, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4675 = true := by
  decide +kernel

theorem tot4675 : totK PA10K2 A10K2.t4675 = [0, 578192132007, 1899606484722, 1801465383762, 505411032061, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
