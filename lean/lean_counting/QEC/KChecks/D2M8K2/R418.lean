import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1672 = true := by
  decide +kernel

theorem tot1672 : totK PD2M8K2 D2M8K2.t1672 = [0, 0, 207845528844, 484540131803, 209390053910, 8747466109, 0, 0] := by
  decide +kernel

theorem rows1673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1673 = true := by
  decide +kernel

theorem tot1673 : totK PD2M8K2 D2M8K2.t1673 = [0, 0, 193691058281, 465107296464, 226049040005, 12551143345, 0, 0] := by
  decide +kernel

theorem rows1674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1674 = true := by
  decide +kernel

theorem tot1674 : totK PD2M8K2 D2M8K2.t1674 = [0, 0, 19735703396, 322740481196, 451732216974, 88925273304, 1242138600, 0] := by
  decide +kernel

theorem rows1675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1675 = true := by
  decide +kernel

theorem tot1675 : totK PD2M8K2 D2M8K2.t1675 = [0, 0, 0, 219782773436, 462641161689, 152061036336, 7182288656, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
