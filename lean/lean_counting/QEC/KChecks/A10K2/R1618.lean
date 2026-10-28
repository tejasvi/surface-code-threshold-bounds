import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6472 = true := by
  decide +kernel

theorem tot6472 : totK PA10K2 A10K2.t6472 = [0, 0, 301533737385, 1345987172117, 2049418866139, 1081340547537, 157718997964, 6318667960, 0, 0] := by
  decide +kernel

theorem rows6473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6473 = true := by
  decide +kernel

theorem tot6473 : totK PA10K2 A10K2.t6473 = [0, 0, 476712794244, 1809256689956, 2057251334275, 625496867880, 24392585150, 0, 0, 0] := by
  decide +kernel

theorem rows6474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6474 = true := by
  decide +kernel

theorem tot6474 : totK PA10K2 A10K2.t6474 = [0, 0, 79759554770, 871214609312, 2126703304373, 1561974874949, 252759818048, 6439430839, 0, 0] := by
  decide +kernel

theorem rows6475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6475 = true := by
  decide +kernel

theorem tot6475 : totK PA10K2 A10K2.t6475 = [0, 0, 469298116613, 1859849081422, 2007866524678, 528720839138, 22108643497, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
