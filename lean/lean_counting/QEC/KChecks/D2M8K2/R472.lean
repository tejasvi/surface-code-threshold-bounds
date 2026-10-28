import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1888 = true := by
  decide +kernel

theorem tot1888 : totK PD2M8K2 D2M8K2.t1888 = [0, 0, 242156157536, 488733266949, 154670113196, 8470662040, 0, 0] := by
  decide +kernel

theorem rows1889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1889 = true := by
  decide +kernel

theorem tot1889 : totK PD2M8K2 D2M8K2.t1889 = [0, 172438341442, 400215943313, 242573362092, 70344910258, 3581949829, 0, 0] := by
  decide +kernel

theorem rows1890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1890 = true := by
  decide +kernel

theorem tot1890 : totK PD2M8K2 D2M8K2.t1890 = [0, 170648880015, 443524479619, 263575036696, 18659338025, 0, 0, 0] := by
  decide +kernel

theorem rows1891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1891 = true := by
  decide +kernel

theorem tot1891 : totK PD2M8K2 D2M8K2.t1891 = [0, 92722701599, 367377812346, 362658043637, 67282688334, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
