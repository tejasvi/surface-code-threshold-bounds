import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5924 = true := by
  decide +kernel

theorem tot5924 : totK PD2M8K2 D2M8K2.t5924 = [78546136620, 265227530610, 377882653325, 173333994076, 8213711289, 0, 0, 0] := by
  decide +kernel

theorem rows5925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5925 = true := by
  decide +kernel

theorem tot5925 : totK PD2M8K2 D2M8K2.t5925 = [180300845383, 454407154516, 264402519241, 26406343020, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5926 = true := by
  decide +kernel

theorem tot5926 : totK PD2M8K2 D2M8K2.t5926 = [157895864527, 458613366233, 273074098602, 19889501550, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5927 = true := by
  decide +kernel

theorem tot5927 : totK PD2M8K2 D2M8K2.t5927 = [0, 238939220875, 512516529239, 146933792650, 2309606161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
