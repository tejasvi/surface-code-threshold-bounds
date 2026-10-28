import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5616 = true := by
  decide +kernel

theorem tot5616 : totK PA10K2 A10K2.t5616 = [0, 0, 474026294606, 1775704195698, 1952639749600, 563694310921, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5617 = true := by
  decide +kernel

theorem tot5617 : totK PA10K2 A10K2.t5617 = [0, 0, 0, 771813220786, 2099054467287, 1544330178894, 341615440371, 25371180993, 0, 0] := by
  decide +kernel

theorem rows5618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5618 = true := by
  decide +kernel

theorem tot5618 : totK PA10K2 A10K2.t5618 = [0, 0, 275388434726, 1189686817708, 1895426103998, 1160408995555, 183748472137, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5619 = true := by
  decide +kernel

theorem tot5619 : totK PA10K2 A10K2.t5619 = [0, 0, 282806832806, 1473835166800, 2175315018803, 774655346576, 46058408420, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
