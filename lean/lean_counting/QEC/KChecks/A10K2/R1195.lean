import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4780 = true := by
  decide +kernel

theorem tot4780 : totK PA10K2 A10K2.t4780 = [0, 0, 274791535979, 1515370446311, 2186415258754, 729059995438, 46692752284, 0, 0, 0] := by
  decide +kernel

theorem rows4781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4781 = true := by
  decide +kernel

theorem tot4781 : totK PA10K2 A10K2.t4781 = [0, 0, 299445560447, 1278574967303, 1955164461619, 1024528393953, 160574319216, 5460492893, 0, 0] := by
  decide +kernel

theorem rows4782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4782 = true := by
  decide +kernel

theorem tot4782 : totK PA10K2 A10K2.t4782 = [0, 0, 465436217816, 1782060376247, 1986281204547, 584225908569, 25027633033, 0, 0, 0] := by
  decide +kernel

theorem rows4783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4783 = true := by
  decide +kernel

theorem tot4783 : totK PA10K2 A10K2.t4783 = [0, 0, 0, 578989242142, 2013583059173, 1684667272977, 350202684490, 24969229125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
