import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7588 = true := by
  decide +kernel

theorem tot7588 : totK PA10K2 A10K2.t7588 = [0, 0, 473180971226, 1740763671599, 1903259672197, 702512355820, 64595321016, 0, 0, 0] := by
  decide +kernel

theorem rows7589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7589 = true := by
  decide +kernel

theorem tot7589 : totK PA10K2 A10K2.t7589 = [0, 0, 306993966079, 1472719941883, 2164594212635, 939220718133, 82708147178, 0, 0, 0] := by
  decide +kernel

theorem rows7590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7590 = true := by
  decide +kernel

theorem tot7590 : totK PA10K2 A10K2.t7590 = [0, 0, 268056436594, 1080198305899, 1920735908423, 1415542465002, 257327435398, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7591 = true := by
  decide +kernel

theorem tot7591 : totK PA10K2 A10K2.t7591 = [0, 0, 440271878393, 1818768227928, 2095021658740, 607201577322, 23620721234, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
