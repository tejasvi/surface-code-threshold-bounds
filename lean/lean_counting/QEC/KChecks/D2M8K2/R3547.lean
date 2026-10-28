import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14188 = true := by
  decide +kernel

theorem tot14188 : totK PD2M8K2 D2M8K2.t14188 = [0, 172021800825, 447795591591, 277190398730, 28468613291, 0, 0, 0] := by
  decide +kernel

theorem rows14189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14189 = true := by
  decide +kernel

theorem tot14189 : totK PD2M8K2 D2M8K2.t14189 = [0, 121862089257, 456582976750, 308296096268, 26777328577, 0, 0, 0] := by
  decide +kernel

theorem rows14190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14190 = true := by
  decide +kernel

theorem tot14190 : totK PD2M8K2 D2M8K2.t14190 = [0, 0, 231998475715, 503514238066, 146699000745, 2484078857, 0, 0] := by
  decide +kernel

theorem rows14191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14191 = true := by
  decide +kernel

theorem tot14191 : totK PD2M8K2 D2M8K2.t14191 = [108461727635, 243413572888, 174610584202, 238156200710, 118265415205, 6818291842, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
