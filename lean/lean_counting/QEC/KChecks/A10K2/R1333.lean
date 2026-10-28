import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5332 = true := by
  decide +kernel

theorem tot5332 : totK PA10K2 A10K2.t5332 = [0, 257394869770, 918645064828, 1569473168109, 1603082985899, 608917175425, 50548650670, 0, 0, 0] := by
  decide +kernel

theorem rows5333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5333 = true := by
  decide +kernel

theorem tot5333 : totK PA10K2 A10K2.t5333 = [0, 523234383636, 1907070454108, 1958781065057, 522064117026, 31863753596, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5334 = true := by
  decide +kernel

theorem tot5334 : totK PA10K2 A10K2.t5334 = [0, 0, 735141389017, 2102768630438, 1635373306876, 378484505236, 25295400199, 0, 0, 0] := by
  decide +kernel

theorem rows5335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5335 = true := by
  decide +kernel

theorem tot5335 : totK PA10K2 A10K2.t5335 = [0, 287747644888, 1275469854871, 2022232517859, 1202103134827, 197008359770, 5453753178, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
