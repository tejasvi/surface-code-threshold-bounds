import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows72 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t72 = true := by
  decide +kernel

theorem tot72 : totK PA10K2 A10K2.t72 = [0, 301744193252, 1502201471929, 2180712018661, 891207619816, 76712913797, 0, 0, 0, 0] := by
  decide +kernel

theorem rows73 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t73 = true := by
  decide +kernel

theorem tot73 : totK PA10K2 A10K2.t73 = [0, 50032118883, 694021889668, 2060856696106, 1675206392718, 391855727320, 25313348169, 0, 0, 0] := by
  decide +kernel

theorem rows74 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t74 = true := by
  decide +kernel

theorem tot74 : totK PA10K2 A10K2.t74 = [0, 427173212875, 1767969474249, 2117449096170, 761405911325, 65469546268, 0, 0, 0, 0] := by
  decide +kernel

theorem rows75 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t75 = true := by
  decide +kernel

theorem tot75 : totK PA10K2 A10K2.t75 = [0, 287047590581, 1271620969669, 2043520162999, 1264723462660, 233853648744, 7151180950, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
