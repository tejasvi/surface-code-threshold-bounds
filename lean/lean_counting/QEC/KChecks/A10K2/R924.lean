import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3696 = true := by
  decide +kernel

theorem tot3696 : totK PA10K2 A10K2.t3696 = [0, 284548233047, 1107608224681, 1860706082986, 1273204769102, 226838040635, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3697 = true := by
  decide +kernel

theorem tot3697 : totK PA10K2 A10K2.t3697 = [0, 218175288971, 1441595096104, 2355814844402, 1026169487481, 89951787083, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3698 = true := by
  decide +kernel

theorem tot3698 : totK PA10K2 A10K2.t3698 = [0, 0, 545090174782, 1903688229040, 1996618952837, 610570222613, 42811788876, 0, 0, 0] := by
  decide +kernel

theorem rows3699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3699 = true := by
  decide +kernel

theorem tot3699 : totK PA10K2 A10K2.t3699 = [0, 0, 445595601406, 1800377034392, 1988091221578, 546584852433, 32523532663, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
