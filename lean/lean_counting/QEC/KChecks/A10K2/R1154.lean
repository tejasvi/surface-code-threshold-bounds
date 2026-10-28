import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4616 = true := by
  decide +kernel

theorem tot4616 : totK PA10K2 A10K2.t4616 = [0, 407636629962, 1662740337587, 2100948901194, 776095550107, 69226627978, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4617 = true := by
  decide +kernel

theorem tot4617 : totK PA10K2 A10K2.t4617 = [0, 306393798244, 1521919542672, 2222563733116, 939814903471, 81506800736, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4618 = true := by
  decide +kernel

theorem tot4618 : totK PA10K2 A10K2.t4618 = [0, 302214352193, 1227276255752, 1928123361228, 1284463083861, 248273328031, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows4619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4619 = true := by
  decide +kernel

theorem tot4619 : totK PA10K2 A10K2.t4619 = [0, 480671717467, 1833323449592, 1989891441567, 598224929789, 37890983068, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
