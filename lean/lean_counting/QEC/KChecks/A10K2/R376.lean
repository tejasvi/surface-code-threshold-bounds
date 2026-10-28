import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1504 = true := by
  decide +kernel

theorem tot1504 : totK PA10K2 A10K2.t1504 = [0, 0, 480154549792, 1852488352386, 2072938177809, 609722948385, 25461131886, 0, 0, 0] := by
  decide +kernel

theorem rows1505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1505 = true := by
  decide +kernel

theorem tot1505 : totK PA10K2 A10K2.t1505 = [0, 0, 0, 579611302481, 1989253056955, 1813232533641, 396430663802, 20029934272, 0, 0] := by
  decide +kernel

theorem rows1506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1506 = true := by
  decide +kernel

theorem tot1506 : totK PA10K2 A10K2.t1506 = [0, 0, 508593201250, 1809574043471, 1974829433929, 748336781141, 74170172794, 0, 0, 0] := by
  decide +kernel

theorem rows1507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1507 = true := by
  decide +kernel

theorem tot1507 : totK PA10K2 A10K2.t1507 = [0, 0, 119585100515, 1028771278385, 2271520832166, 1480718200866, 234173043212, 8047840951, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
