import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4556 = true := by
  decide +kernel

theorem tot4556 : totK PA10K2 A10K2.t4556 = [465631835236, 1768188486486, 2005543733943, 586867807658, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4557 = true := by
  decide +kernel

theorem tot4557 : totK PA10K2 A10K2.t4557 = [0, 654971171023, 1999215239123, 1699739567754, 410340198602, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4558 = true := by
  decide +kernel

theorem tot4558 : totK PA10K2 A10K2.t4558 = [254295448775, 1094210047392, 1878091984343, 1267982453741, 219255687892, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4559 = true := by
  decide +kernel

theorem tot4559 : totK PA10K2 A10K2.t4559 = [583317622402, 1953688128168, 1788250154546, 464629237241, 31941609474, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
