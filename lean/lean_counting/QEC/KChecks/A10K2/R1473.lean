import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5892 = true := by
  decide +kernel

theorem tot5892 : totK PA10K2 A10K2.t5892 = [0, 0, 0, 265397247896, 1153154941225, 1815987165186, 1151437997174, 236055009053, 11427838733, 0] := by
  decide +kernel

theorem rows5893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5893 = true := by
  decide +kernel

theorem tot5893 : totK PA10K2 A10K2.t5893 = [0, 0, 0, 461985974218, 1660881925204, 1879726285287, 622449215703, 51963961291, 0, 0] := by
  decide +kernel

theorem rows5894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5894 = true := by
  decide +kernel

theorem tot5894 : totK PA10K2 A10K2.t5894 = [0, 0, 0, 113126642960, 1248648086853, 2299801592059, 957266033866, 72234150448, 0, 0] := by
  decide +kernel

theorem rows5895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5895 = true := by
  decide +kernel

theorem tot5895 : totK PA10K2 A10K2.t5895 = [0, 0, 0, 0, 515578994673, 1944750660728, 1667845604235, 393829178573, 25807237568, 0] := by
  decide +kernel

end QECKChecks.A10K2
