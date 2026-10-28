import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t572 = true := by
  decide +kernel

theorem tot572 : totK PA10K2 A10K2.t572 = [0, 304031809754, 1291684864122, 1900987055760, 1129987827484, 219161865151, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t573 = true := by
  decide +kernel

theorem tot573 : totK PA10K2 A10K2.t573 = [0, 459336103421, 1832040702371, 2019988288745, 616896729042, 41740271405, 0, 0, 0, 0] := by
  decide +kernel

theorem rows574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t574 = true := by
  decide +kernel

theorem tot574 : totK PA10K2 A10K2.t574 = [0, 0, 455767485160, 1899020825364, 1853072347101, 431363147998, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t575 = true := by
  decide +kernel

theorem tot575 : totK PA10K2 A10K2.t575 = [0, 481676879802, 1657230915744, 1731407221549, 778918190645, 149715258580, 5718040558, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
