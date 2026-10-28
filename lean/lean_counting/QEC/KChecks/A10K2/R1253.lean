import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5012 = true := by
  decide +kernel

theorem tot5012 : totK PA10K2 A10K2.t5012 = [0, 201436515068, 987896090436, 1927342779668, 1316059294178, 241312777167, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5013 = true := by
  decide +kernel

theorem tot5013 : totK PA10K2 A10K2.t5013 = [0, 257083911228, 1409745551462, 2187625858909, 950323535229, 89734349891, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5014 = true := by
  decide +kernel

theorem tot5014 : totK PA10K2 A10K2.t5014 = [0, 311769148082, 1250761080177, 1831456272040, 1238882458054, 251881798613, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5015 = true := by
  decide +kernel

theorem tot5015 : totK PA10K2 A10K2.t5015 = [0, 491470360234, 1820212486253, 1947509569086, 526424333876, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
