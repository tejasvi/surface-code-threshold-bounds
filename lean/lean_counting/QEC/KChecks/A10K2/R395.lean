import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1580 = true := by
  decide +kernel

theorem tot1580 : totK PA10K2 A10K2.t1580 = [0, 0, 0, 460467164459, 1850194711181, 1926561039172, 432954175051, 25633273041, 0, 0] := by
  decide +kernel

theorem rows1581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1581 = true := by
  decide +kernel

theorem tot1581 : totK PA10K2 A10K2.t1581 = [0, 0, 0, 718221072173, 2130487032348, 1610921166208, 334677184890, 12918102615, 0, 0] := by
  decide +kernel

theorem rows1582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1582 = true := by
  decide +kernel

theorem tot1582 : totK PA10K2 A10K2.t1582 = [0, 0, 0, 503063439174, 1821078356908, 1810705376280, 462002437641, 30973630058, 0, 0] := by
  decide +kernel

theorem rows1583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1583 = true := by
  decide +kernel

theorem tot1583 : totK PA10K2 A10K2.t1583 = [0, 0, 0, 298252571475, 1582568127574, 2031819384587, 628765844794, 38031574496, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
