import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1536 = true := by
  decide +kernel

theorem tot1536 : totK PA10K2 A10K2.t1536 = [0, 518135067396, 1778977670068, 1817619302929, 602802957763, 58946169666, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1537 = true := by
  decide +kernel

theorem tot1537 : totK PA10K2 A10K2.t1537 = [0, 0, 717535641113, 2058910484437, 1497645322150, 323387824836, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows1538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1538 = true := by
  decide +kernel

theorem tot1538 : totK PA10K2 A10K2.t1538 = [0, 491201868289, 1533567204010, 1639382251822, 882218158315, 168629528027, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows1539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1539 = true := by
  decide +kernel

theorem tot1539 : totK PA10K2 A10K2.t1539 = [0, 318686474193, 1543919944866, 1995889444603, 693205738237, 53385992088, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
