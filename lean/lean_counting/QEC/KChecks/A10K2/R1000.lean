import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4000 = true := by
  decide +kernel

theorem tot4000 : totK PA10K2 A10K2.t4000 = [0, 442007375393, 1720186988446, 1990951173842, 697389566253, 53949312070, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4001 = true := by
  decide +kernel

theorem tot4001 : totK PA10K2 A10K2.t4001 = [0, 540969523310, 1913796738136, 2017660883520, 599632238098, 37621296095, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4002 = true := by
  decide +kernel

theorem tot4002 : totK PA10K2 A10K2.t4002 = [0, 0, 756174418910, 2226474544885, 1713241288264, 304594854884, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4003 = true := by
  decide +kernel

theorem tot4003 : totK PA10K2 A10K2.t4003 = [0, 0, 476995557736, 1770387863051, 2141037075622, 744008358290, 56126419230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
