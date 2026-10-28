import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4184 = true := by
  decide +kernel

theorem tot4184 : totK PA10K2 A10K2.t4184 = [580977587835, 1970116187307, 1811053078008, 432368329340, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4185 = true := by
  decide +kernel

theorem tot4185 : totK PA10K2 A10K2.t4185 = [181236568781, 1100399494067, 2057485790760, 1204645265493, 241849420887, 20070762815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4186 = true := by
  decide +kernel

theorem tot4186 : totK PA10K2 A10K2.t4186 = [133373834325, 783091203413, 1863833378333, 1593180074355, 339888119649, 10760911071, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4187 = true := by
  decide +kernel

theorem tot4187 : totK PA10K2 A10K2.t4187 = [493645564158, 1817806696351, 1941195473062, 567095832327, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
