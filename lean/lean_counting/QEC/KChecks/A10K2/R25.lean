import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t100 = true := by
  decide +kernel

theorem tot100 : totK PA10K2 A10K2.t100 = [0, 203925314903, 1000331081821, 1788137579302, 1313123974519, 328228012657, 15911743486, 0, 0, 0] := by
  decide +kernel

theorem rows101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t101 = true := by
  decide +kernel

theorem tot101 : totK PA10K2 A10K2.t101 = [0, 534995996399, 1867467654722, 1771332735503, 479263281098, 31936107789, 0, 0, 0, 0] := by
  decide +kernel

theorem rows102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t102 = true := by
  decide +kernel

theorem tot102 : totK PA10K2 A10K2.t102 = [0, 0, 807337831624, 2347052046733, 1330906812471, 116192583074, 0, 0, 0, 0] := by
  decide +kernel

theorem rows103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t103 = true := by
  decide +kernel

theorem tot103 : totK PA10K2 A10K2.t103 = [580977587835, 1775810864323, 1554587255720, 471977876143, 257099157048, 103171629428, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
