import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t812 = true := by
  decide +kernel

theorem tot812 : totK PA10K2 A10K2.t812 = [285766734819, 1047461729442, 1595569837729, 1489838650600, 584729775239, 50499610055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t813 = true := by
  decide +kernel

theorem tot813 : totK PA10K2 A10K2.t813 = [306766947263, 1553760056352, 2235011771950, 914208762556, 76854630649, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t814 = true := by
  decide +kernel

theorem tot814 : totK PA10K2 A10K2.t814 = [195174425874, 942735788841, 1920901349909, 1536675865235, 369649257260, 25219735747, 0, 0, 0, 0] := by
  decide +kernel

theorem rows815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t815 = true := by
  decide +kernel

theorem tot815 : totK PA10K2 A10K2.t815 = [546569041324, 1899573597329, 1939470610129, 539881516949, 32780555804, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
