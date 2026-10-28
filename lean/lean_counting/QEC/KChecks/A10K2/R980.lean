import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3920 = true := by
  decide +kernel

theorem tot3920 : totK PA10K2 A10K2.t3920 = [0, 0, 539000210498, 1845861180440, 1928229465625, 659714202118, 57246357170, 0, 0, 0] := by
  decide +kernel

theorem rows3921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3921 = true := by
  decide +kernel

theorem tot3921 : totK PA10K2 A10K2.t3921 = [0, 0, 327737319032, 1551320900384, 2171362944577, 834982472551, 63507317963, 0, 0, 0] := by
  decide +kernel

theorem rows3922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3922 = true := by
  decide +kernel

theorem tot3922 : totK PA10K2 A10K2.t3922 = [0, 0, 0, 530726071716, 2027431567548, 2009187925871, 441456555428, 13231026584, 0, 0] := by
  decide +kernel

theorem rows3923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3923 = true := by
  decide +kernel

theorem tot3923 : totK PA10K2 A10K2.t3923 = [0, 320479959089, 932003970308, 886912670229, 1037066054064, 1263897259959, 518279520850, 49137536365, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
