import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1788 = true := by
  decide +kernel

theorem tot1788 : totK PA10K2 A10K2.t1788 = [0, 0, 452388186593, 1796799542531, 1968284224780, 590616132260, 30252402453, 0, 0, 0] := by
  decide +kernel

theorem rows1789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1789 = true := by
  decide +kernel

theorem tot1789 : totK PA10K2 A10K2.t1789 = [0, 0, 0, 496535640835, 1928821634575, 1775169897763, 386670361708, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1790 = true := by
  decide +kernel

theorem tot1790 : totK PA10K2 A10K2.t1790 = [0, 0, 458265347460, 1550834409583, 1768541444771, 805799509163, 134830190562, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1791 = true := by
  decide +kernel

theorem tot1791 : totK PA10K2 A10K2.t1791 = [0, 0, 239271980377, 1395338269989, 2160090941770, 925373103140, 63421051570, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
