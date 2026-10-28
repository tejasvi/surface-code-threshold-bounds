import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6604 = true := by
  decide +kernel

theorem tot6604 : totK PA10K2 A10K2.t6604 = [0, 541450865991, 1958137511090, 2104905506146, 631354544396, 26102305433, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6605 = true := by
  decide +kernel

theorem tot6605 : totK PA10K2 A10K2.t6605 = [0, 0, 585073645252, 2076256793193, 2011486799150, 443887811916, 13543209714, 0, 0, 0] := by
  decide +kernel

theorem rows6606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6606 = true := by
  decide +kernel

theorem tot6606 : totK PA10K2 A10K2.t6606 = [0, 0, 622669460045, 1934025325034, 1828415042643, 595421125222, 49165311630, 0, 0, 0] := by
  decide +kernel

theorem rows6607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6607 = true := by
  decide +kernel

theorem tot6607 : totK PA10K2 A10K2.t6607 = [0, 0, 472372038844, 1856766968076, 2056536386435, 546434256920, 31222411477, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
