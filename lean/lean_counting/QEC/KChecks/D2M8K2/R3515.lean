import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14060 = true := by
  decide +kernel

theorem tot14060 : totK PD2M8K2 D2M8K2.t14060 = [0, 179380513928, 469156851238, 241332221275, 14640859392, 0, 0, 0] := by
  decide +kernel

theorem rows14061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14061 = true := by
  decide +kernel

theorem tot14061 : totK PD2M8K2 D2M8K2.t14061 = [0, 65600037915, 290571441973, 356983402573, 175004323652, 21396654552, 0, 0] := by
  decide +kernel

theorem rows14062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14062 = true := by
  decide +kernel

theorem tot14062 : totK PD2M8K2 D2M8K2.t14062 = [0, 0, 195955638866, 482415858338, 206961486954, 7994456143, 0, 0] := by
  decide +kernel

theorem rows14063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14063 = true := by
  decide +kernel

theorem tot14063 : totK PD2M8K2 D2M8K2.t14063 = [0, 67104705643, 245344492191, 389174304515, 182265231498, 8100177866, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
