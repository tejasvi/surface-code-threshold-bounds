import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1628 = true := by
  decide +kernel

theorem tot1628 : totK PA10K2 A10K2.t1628 = [0, 0, 474166020316, 1753822487086, 1958214053390, 577285252900, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows1629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1629 = true := by
  decide +kernel

theorem tot1629 : totK PA10K2 A10K2.t1629 = [0, 0, 81708943773, 945036328900, 2087675789196, 1424039760224, 302023189162, 25734533292, 0, 0] := by
  decide +kernel

theorem rows1630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1630 = true := by
  decide +kernel

theorem tot1630 : totK PA10K2 A10K2.t1630 = [0, 0, 236817354085, 1094069568367, 1881229049758, 1248613876871, 212013707853, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1631 = true := by
  decide +kernel

theorem tot1631 : totK PA10K2 A10K2.t1631 = [0, 0, 581540748246, 1861725747186, 1794935546108, 506906456971, 31941609474, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
