import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1656 = true := by
  decide +kernel

theorem tot1656 : totK PA10K2 A10K2.t1656 = [0, 298064684126, 1485164233318, 2132819142193, 812543777702, 53383554103, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1657 = true := by
  decide +kernel

theorem tot1657 : totK PA10K2 A10K2.t1657 = [0, 150713694566, 914906750821, 2002385976296, 1383232945524, 248638969737, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1658 = true := by
  decide +kernel

theorem tot1658 : totK PA10K2 A10K2.t1658 = [0, 117348215122, 1018481284654, 2122641412338, 1417906428446, 272870710290, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows1659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1659 = true := by
  decide +kernel

theorem tot1659 : totK PA10K2 A10K2.t1659 = [0, 0, 454575959798, 1808476793250, 1901859176523, 467493179780, 26479096260, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
