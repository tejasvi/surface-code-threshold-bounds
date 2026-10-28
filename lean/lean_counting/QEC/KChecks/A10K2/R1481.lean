import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5924 = true := by
  decide +kernel

theorem tot5924 : totK PA10K2 A10K2.t5924 = [0, 534673539444, 1929565606735, 1925178221445, 458346631517, 13149917422, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5925 = true := by
  decide +kernel

theorem tot5925 : totK PA10K2 A10K2.t5925 = [0, 503927570364, 1764590072422, 1809589554314, 549442492568, 50267370225, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5926 = true := by
  decide +kernel

theorem tot5926 : totK PA10K2 A10K2.t5926 = [0, 111833022044, 1239780347743, 2251110604891, 910299321056, 77820506896, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5927 = true := by
  decide +kernel

theorem tot5927 : totK PA10K2 A10K2.t5927 = [338679903066, 1144714035763, 1335977001832, 1000667253945, 747718617943, 187952782646, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
