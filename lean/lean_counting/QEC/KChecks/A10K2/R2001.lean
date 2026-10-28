import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8004 = true := by
  decide +kernel

theorem tot8004 : totK PA10K2 A10K2.t8004 = [0, 0, 276411238399, 1216747267779, 1965634769241, 1117281686521, 194868207022, 5460492893, 0, 0] := by
  decide +kernel

theorem rows8005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8005 = true := by
  decide +kernel

theorem tot8005 : totK PA10K2 A10K2.t8005 = [0, 0, 280123126306, 1383158376510, 2013196063229, 995152249941, 145025507585, 9566038846, 0, 0] := by
  decide +kernel

theorem rows8006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8006 = true := by
  decide +kernel

theorem tot8006 : totK PA10K2 A10K2.t8006 = [0, 0, 0, 455985908311, 1804700555908, 1999440620840, 549330918399, 28839085606, 0, 0] := by
  decide +kernel

theorem rows8007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8007 = true := by
  decide +kernel

theorem tot8007 : totK PA10K2 A10K2.t8007 = [0, 0, 0, 552966263496, 2040070011255, 1857601838331, 299376983652, 5420028275, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
