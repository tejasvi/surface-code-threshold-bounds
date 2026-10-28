import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t808 = true := by
  decide +kernel

theorem tot808 : totK PA10K2 A10K2.t808 = [0, 0, 540032415453, 1837232706359, 1762927602552, 477040429113, 31082886609, 0, 0, 0] := by
  decide +kernel

theorem rows809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t809 = true := by
  decide +kernel

theorem tot809 : totK PA10K2 A10K2.t809 = [0, 521804831435, 1713497137558, 1876407611469, 700147118320, 65527055973, 0, 0, 0, 0] := by
  decide +kernel

theorem rows810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t810 = true := by
  decide +kernel

theorem tot810 : totK PA10K2 A10K2.t810 = [0, 39815911663, 993005182662, 2312623194018, 1238247243958, 110334261200, 0, 0, 0, 0] := by
  decide +kernel

theorem rows811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t811 = true := by
  decide +kernel

theorem tot811 : totK PA10K2 A10K2.t811 = [0, 486228783549, 1757082442682, 1900831670893, 727619103545, 130310238196, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
