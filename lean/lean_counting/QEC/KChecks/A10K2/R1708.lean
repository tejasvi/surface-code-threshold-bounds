import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6832 = true := by
  decide +kernel

theorem tot6832 : totK PA10K2 A10K2.t6832 = [0, 0, 486036167111, 1801278918718, 1806918267733, 484198035011, 30780440178, 0, 0, 0] := by
  decide +kernel

theorem rows6833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6833 = true := by
  decide +kernel

theorem tot6833 : totK PA10K2 A10K2.t6833 = [0, 441487391689, 1718337545645, 1894462975894, 665212069355, 64539709712, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6834 = true := by
  decide +kernel

theorem tot6834 : totK PA10K2 A10K2.t6834 = [0, 291093484992, 1258090430818, 1938792605492, 1072640791985, 167996216351, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows6835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6835 = true := by
  decide +kernel

theorem tot6835 : totK PA10K2 A10K2.t6835 = [0, 539466270671, 1914858097836, 2048376311966, 589232212050, 37396946132, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
